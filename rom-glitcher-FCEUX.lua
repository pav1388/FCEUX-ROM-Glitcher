-- ROM Glitcher: Instruction Inverter для FCEUX
-- Алгоритм поиска глитчей через инвертирование инструкций
--
-- Идея и оригинальная Си программа: Беларус учит русский aka perfect_genius
-- Lua-реализация: pav13
-- https://github.com/pav1388/FCEUX-ROM-Glitcher

-- ============================================================
local SCRIPT_VERSION = "0.3.1" -- "20.04.2026"
local FCEUX_MIN_VERSION = "2.2.3"
local LANGUAGE = nil      -- Язык интерфейса
local SAVE_MOD_PATH = ""  -- Путь сохранения модифицированных ROM-файлов ("C:\\mod-roms")
local DEBUG_MODE = false  -- Вывод отладочной информации в log-файл
local RANDOM_SEED = true  -- Случайный сид при перемешивании инструкций

-- ==================== КОНСТАНТЫ ====================
local START_LENGTH_DIV = 16      -- Начальный размер окна (1/16 от всех инструкций)
local INSTR_ADDR_INDEX = 1       -- Индекс адреса инструкции в таблице
local INIT_VAL_INDEX = 2         -- Индекс исходного значения опкода
local HEADER_SIZE = 16           -- Размер заголовка в байтах
local LANG_FILE = "rom-glitcher-FCEUX-lang.lng"
local LOG_FILE = "rom-glitcher-FCEUX-debug.log"
local CONFIG_FILE = "rom-glitcher-FCEUX-config.cfg"
local DEFAULT_GROUP = "BEQ_BNE"  -- Группа инструкций по-умолчанию

-- ==================== ГЛОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ====================
local lang_strings = {}            -- Хранилище локализованных строк
local current_input = {}           -- Текущий ввод с клавиатуры
local rom_filename = ""            -- Имя текущего ROM-файла
local rom_hash = nil               -- Хэш текущего ROM-файла 
local rom_size = 0                 -- Размер ROM в байтах
local rom_backup = nil             -- Резервная копия ROM
local trainer_size = 0             -- Размер тренера в байтах
local temp_savestate = nil         -- Контейнер для состояния игры
local total_instructions = 0       -- Общее количество найденных инструкций
local cur_state                    -- Текущее состояние поиска
local prev_state                   -- Предыдущее состояние поиска
local pre_local_state              -- Состояние поиска до локализации
local qt_version = nil             -- Версия эмулятора
local instr_select_mode = false    -- Режим выбора инструкций для поиска
local active_instr_groups = {}     -- Хранит выбранные для поиска инструкции
local instr_select_cursor = 1      -- Позиция курсора в меню выбора инструкции
local available_instr_groups = {}  -- Список доступных типов инструкций
local cached_valid_nes_instr = {}  -- Кэшированная таблица валидных NES инструкций
local init_instr_table = {}        -- Копия таблицы инструкций для поиска
local key_states = {}              -- Таблица состояния клавиш


-- ==================== ТАБЛИЦЫ ДАННЫХ ====================
-- Таблица инструкций для поиска
local instr_table = {
    -- [опкод] = {имя, инвертированное_значение, имя_группы}
    -- Условные переходы
    [0xF0] = {"BEQ", 0xD0, "BEQ_BNE"},  -- Branch if Equal -> Branch if Not Equal
    [0xD0] = {"BNE", 0xF0, "BEQ_BNE"},  -- Branch if Not Equal -> Branch if Equal
    [0x90] = {"BCC", 0xB0, "BCC_BCS"},  -- Branch if Carry Clear -> Branch if Carry Set
    [0xB0] = {"BCS", 0x90, "BCC_BCS"},  -- Branch if Carry Set -> Branch if Carry Clear
    [0x10] = {"BPL", 0x30, "BPL_BMI"},  -- Branch if PLus -> Branch if MInus
    [0x30] = {"BMI", 0x10, "BPL_BMI"},  -- Branch if MInus -> Branch if PLus
    [0x50] = {"BVC", 0x70, "BVC_BVS"},  -- Branch if oVerflow Clear -> Branch if oVerflow Set
    [0x70] = {"BVS", 0x50, "BVC_BVS"},  -- Branch if oVerflow Set -> Branch if oVerflow Clear
    -- Флаги
    [0x18] = {"CLC", 0x38, "CLC_SEC"},  -- CLear Carry -> SEt Carry
    [0x38] = {"SEC", 0x18, "CLC_SEC"},  -- SEt Carry -> CLear Carry
    [0x58] = {"CLI", 0x78, "CLI_SEI"},  -- CLear Interrupt -> SEt Interrupt
    [0x78] = {"SEI", 0x58, "CLI_SEI"},  -- SEt Interrupt -> CLear Interrupt
    [0xD8] = {"CLD", 0xF8, "CLD_SED"},  -- CLear Decimal -> SEt Decimal
    [0xF8] = {"SED", 0xD8, "CLD_SED"},  -- SEt Decimal -> CLear Decimal
    -- Регистровые операции
    [0xAA] = {"TAX", 0x8A, "TAX_TXA"},  -- Transfer A to X -> Transfer X to A
    [0x8A] = {"TXA", 0xAA, "TAX_TXA"},  -- Transfer X to A -> Transfer A to X
    [0xA8] = {"TAY", 0x98, "TAY_TYA"},  -- Transfer A to Y -> Transfer Y to A
    [0x98] = {"TYA", 0xA8, "TAY_TYA"},  -- Transfer Y to A -> Transfer A to Y
    [0xBA] = {"TSX", 0x9A, "TSX_TXS"},  -- Transfer Stack pointer to X -> Transfer X to Stack pointer
    [0x9A] = {"TXS", 0xBA, "TSX_TXS"},  -- Transfer X to Stack pointer -> Transfer Stack pointer to X
    -- Ротации
    [0x2A] = {"ROL", 0x6A, "ROL_ROR"},  -- ROtate Left -> ROtate Right
    [0x6A] = {"ROR", 0x2A, "ROL_ROR"},  -- ROtate Right -> ROtate Left
    -- Инкремент/декремент (регистры)
    [0xE8] = {"INX", 0xCA, "INX_DEX"},  -- INcrement X -> DEcrement X
    [0xCA] = {"DEX", 0xE8, "INX_DEX"},  -- DEcrement X -> INcrement X
    [0xC8] = {"INY", 0x88, "INY_DEY"},  -- INcrement Y -> DEcrement Y
    [0x88] = {"DEY", 0xC8, "INY_DEY"},  -- DEcrement Y -> INcrement Y
    -- Логические операции
    [0x29] = {"AND", 0x49, "AND_EOR"},  -- AND -> Exclusive OR
    [0x49] = {"EOR", 0x29, "AND_EOR"},  -- Exclusive OR -> AND
    -- Операции со стеком
    [0x48] = {"PHA", 0x68, "PHA_PLA"},  -- PusH Accumulator -> PulL Accumulator
    [0x68] = {"PLA", 0x48, "PHA_PLA"},  -- PulL Accumulator -> PusH Accumulator
    [0x08] = {"PHP", 0x28, "PHP_PLP"},  -- PusH Processor status -> PulL Processor status
    [0x28] = {"PLP", 0x08, "PHP_PLP"},  -- PulL Processor status -> PusH Processor status
}

-- Таблица клавиш управления (описаний действий в меню)
local keys = {
    key_1 = { value = "Z", desc_search = "", desc_select = "" },
    key_2 = { value = "X", desc_search = "", desc_select = "" },
    key_3 = { value = "C", desc_search = "", desc_select = "" },
    key_4 = { value = "V", desc_search = "", desc_select = "" },
    key_5 = { value = "B", desc_search = "", desc_select = "" },
    key_6 = { value = "N", desc_search = "", desc_select = "" },
    key_7 = { value = "M", desc_search = "", desc_select = "" }
}

-- Шаблон для создания таблицы состояния поиска
local function state_template()
    return {
        instructions = {},          -- Список инструкций-кандидатов
        window_start = 0,           -- Начало текущего окна
        window_size = 0,            -- Размер текущего окна
        step = 0,                   -- Номер текущего шага
        search_localizing = false,  -- Фаза локализации
        search_active = false,      -- Поиск активен
        search_done = false,        -- Поиск завершен успешно
        search_fail = false         -- Поиск завершен неудачно
    }
end

-- Инициализация таблиц состояний
cur_state = state_template()        -- Текущее состояние
prev_state = state_template()       -- Предыдущее состояние
pre_local_state = state_template()  -- Состояние до локализации

-- Таблица преобразования кириллицы ("Ёё" не используются)
local conversion_table_cyr = {
    -- [второй байт UTF-8 символа] = байт символа в кодировке WIN1251
    [0x90] = 0xC0, [0x91] = 0xC1, [0x92] = 0xC2, [0x93] = 0xC3, [0x94] = 0xC4,
    [0x95] = 0xC5, [0x96] = 0xC6, [0x97] = 0xC7, [0x98] = 0xC8, [0x99] = 0xC9,
    [0x9A] = 0xCA, [0x9B] = 0xCB, [0x9C] = 0xCC, [0x9D] = 0xCD, [0x9E] = 0xCE,
    [0x9F] = 0xCF, [0xA0] = 0xD0, [0xA1] = 0xD1, [0xA2] = 0xD2, [0xA3] = 0xD3,
    [0xA4] = 0xD4, [0xA5] = 0xD5, [0xA6] = 0xD6, [0xA7] = 0xD7, [0xA8] = 0xD8,
    [0xA9] = 0xD9, [0xAA] = 0xDA, [0xAB] = 0xDB, [0xAC] = 0xDC, [0xAD] = 0xDD,
    [0xAE] = 0xDE, [0xAF] = 0xDF, [0xB0] = 0xE0, [0xB1] = 0xE1, [0xB2] = 0xE2,
    [0xB3] = 0xE3, [0xB4] = 0xE4, [0xB5] = 0xE5, [0xB6] = 0xE6, [0xB7] = 0xE7,
    [0xB8] = 0xE8, [0xB9] = 0xE9, [0xBA] = 0xEA, [0xBB] = 0xEB, [0xBC] = 0xEC,
    [0xBD] = 0xED, [0xBE] = 0xEE, [0xBF] = 0xEF, [0x80] = 0xF0, [0x81] = 0xF1,
    [0x82] = 0xF2, [0x83] = 0xF3, [0x84] = 0xF4, [0x85] = 0xF5, [0x86] = 0xF6,
    [0x87] = 0xF7, [0x88] = 0xF8, [0x89] = 0xF9, [0x8A] = 0xFA, [0x8B] = 0xFB,
    [0x8C] = 0xFC, [0x8D] = 0xFD, [0x8E] = 0xFE, [0x8F] = 0xFF
}

-- Таблица замены символов с диакретикой
local conversion_table_dia = {
    ["á"] = "a", ["é"] = "e", ["í"] = "i", ["ó"] = "o", ["ú"] = "u",
    ["Á"] = "A", ["É"] = "E", ["Í"] = "I", ["Ó"] = "O", ["Ú"] = "U",
    ["à"] = "a", ["è"] = "e", ["ì"] = "i", ["ò"] = "o", ["ù"] = "u",
    ["À"] = "A", ["È"] = "E", ["Ì"] = "I", ["Ò"] = "O", ["Ù"] = "U",
    ["â"] = "a", ["ê"] = "e", ["î"] = "i", ["ô"] = "o", ["û"] = "u",
    ["Â"] = "A", ["Ê"] = "E", ["Î"] = "I", ["Ô"] = "O", ["Û"] = "U",
    ["ä"] = "ae", ["ë"] = "e", ["ï"] = "i", ["ö"] = "oe", ["ü"] = "ue", ["ÿ"] = "y",
    ["Ä"] = "Ae", ["Ë"] = "E", ["Ï"] = "I", ["Ö"] = "Oe", ["Ü"] = "Ue", ["Ÿ"] = "Y",
    ["ã"] = "a", ["ñ"] = "n", ["õ"] = "o",
    ["Ã"] = "A", ["Ñ"] = "N", ["Õ"] = "O",
    ["ç"] = "c", ["Ç"] = "C",
    ["ß"] = "ss",
}

-- ==================== ОБЪЯВЛЕНИЯ ФУНКЦИЙ ====================
-- Функции локализации
local function lang_load(lang) end
local function tr(key, ...) end
local function convert_encoding(str, lang) end
local function update_key_desc() end
local function lang_ask() end

-- Функции утилиты
local function clear_table(t) end
local function rom_read_byte(addr) end
local function rom_read_byte_signed(addr) end
local function rom_write_byte(addr, val) end
local function is_necessary_instruction(opcode) end
local function get_inverted_opcode(opcode) end
local function get_opcode_name(opcode) end
local function is_valid_nes_instruction(opcode) end

-- Функции поиска и обработки шагов поиска
local function find_instructions() end
local function restore_instructions() end
local function invert_instructions() end
local function shuffle_instructions() end
local function copy_search_state(src, dst) end
local function has_search_state(state) end
local function process_step1() end
local function process_step2() end
local function process_step3() end

-- Функции вывода
local function debug_log(msg) end
local function print_line(msg) end
local function print_error(msg) end
local function print_action(msg) end
local function print_separator() end
local function menu_start() end
local function menu_select() end
local function menu_search() end
local function menu_end_search() end

-- Функции выбора групп инструкций
local function collect_instruction_types() end
local function update_active_instructions() end

-- Функции работы с конфигурацией
local function create_key_mapping() end
local function config_save() end
local function config_load() end

-- Основные функции
local function emu_frame_advance(n) end
local function savestate_save() end
local function savestate_load() end
local function emu_soft_reset() end
local function new_search() end
local function create_rom_backup() end
local function restore_rom_backup() end
local function save_mod_rom() end
local function check_rom_hash() end

-- Обработка ввода
local function is_key_pressed(key_name) end
local function is_key_released(key_name) end
local function process_input() end

-- Инициализация
local function end_script() end

-- Основной цикл
local function main_loop() end

-- ==================== ФУНКЦИИ ЛОКАЛИЗАЦИИ ====================
-- Парсер файла локализации
function lang_load(lang)
    if not lang then lang = LANGUAGE end
    
    debug_log("lang_load: start, lang=" .. tostring(lang))
    
    local success, file = pcall(io.open, LANG_FILE, "r")
    if not success or not file then
        debug_log("FAILED lang_load: cannot open " .. LANG_FILE)
        return false
    end
    
    lang_strings = {}
    
    local current_section = nil
    local found_target = false
    local found_default = false
    local found_count = 0
    local default_section_data = {}
    
    for line in file:lines() do
        line = line:match("^%s*(.-)%s*$")
        
        if line ~= "" then
            local section = line:match("^%[([%a_]+)%]$")
            if section then
                current_section = section
                debug_log("lang_load: found section [" .. section .. "]")
                
                if section == lang then
                    found_target = true
                    found_default = false
                elseif section == LANGUAGE then
                    found_default = true
                    found_target = false
                    default_section_data = {}
                else
                    found_target = false
                    found_default = false
                end
            elseif current_section then
                local key, value = line:match("^([^=]+)=(.*)$")
                if key and value then
                    key = key:match("^%s*(.-)%s*$")
                    value = value:match("^%s*(.-)%s*$")
                    
                    if found_target then
                        lang_strings[key] = value
                        found_count = found_count + 1
                        debug_log(string.format("lang_load: [%s] %s=%s", 
                                               lang, key, value))
                    elseif found_default and current_section == LANGUAGE then
                        default_section_data[key] = value
                        debug_log(string.format("lang_load: [default] %s=%s", 
                                               key, value))
                    end
                end
            end
        end
    end
    
    file:close()
    
    if not next(lang_strings) then
        debug_log("lang_load: target section '" .. lang 
                        .. "' not found, using default '" .. LANGUAGE .. "'")
        
        for key, value in pairs(default_section_data) do
            lang_strings[key] = value
        end
        
        if not next(lang_strings) then
            debug_log("FAILED lang_load: default section '" 
                        .. LANGUAGE .. "' not found either")
            return false
        end
    end
    
    update_key_desc()
    
    debug_log("lang_load: end, loaded " .. tostring(found_count)
            .. " strings for language '" .. (found_target and lang or LANGUAGE) .. "'")
    return true
end

-- Получение локализованной строки
function tr(key, ...)
    local str = nil
    
    if lang_strings[key] then
        str = lang_strings[key]
    else
        str = key
        debug_log("FAILED tr: missing key '" .. key .. "'")
    end
    
    if select('#', ...) > 0 then
        return string.format(str, ...)
    end
    return str
end

-- Преобразование кодировки для не Qt версии эмулятора
function convert_encoding(str, lang)
    if qt_version then
        return str
    end
    
    if lang == nil or lang == "en" then
        return str
    end
    
    if lang == "ru" then
        local str_len = #str
		local bytes = {}
		
		for i = 1, str_len do
			bytes[i] = 0
		end
		
		local out_pos = 1
		local i = 1
		
		while i <= str_len do
			local b1 = str:byte(i)
			
			if (b1 == 0xD0 or b1 == 0xD1) and i < str_len then
				local b2 = str:byte(i + 1)
				bytes[out_pos] = conversion_table_cyr[b2] or b2
				out_pos = out_pos + 1
				i = i + 2
			else
				bytes[out_pos] = b1
				out_pos = out_pos + 1
				i = i + 1
			end
		end
		
		return string.char(unpack(bytes, 1, out_pos - 1))
    end
    
    -- Для es, pt, de, it
	local result = str
    for from, to in pairs(conversion_table_dia) do
        result = result:gsub(from, to)
    end
    return result
end

-- Локализация описаний действий клавиш
function update_key_desc()
    keys.key_1.desc_search = tr("step1_desc")
    keys.key_2.desc_search = tr("step2_desc")
    keys.key_3.desc_search = tr("step3_desc")
    keys.key_4.desc_search = tr("undo_desc")
    keys.key_5.desc_search = tr("back_desc")
    keys.key_6.desc_search = tr("new_search_desc")
    keys.key_7.desc_search = tr("save_rom_desc")
    keys.key_1.desc_select = tr("cursor_up")
    keys.key_2.desc_select = tr("confirm")
    keys.key_3.desc_select = tr("cursor_down")
    keys.key_4.desc_select = tr("select_all")
    keys.key_5.desc_select = tr("go_back")
    keys.key_6.desc_select = tr("start_new")
end

-- Запроса языка интерфейса у пользователя
function lang_ask()
    print_separator()
    print_line("--- LANGUAGE SELECTION ---")
    print_line("")
    print_line("  [" .. keys.key_1.value .. "] - English (en)")
    print_line("   [" .. keys.key_2.value .. "] - Russian (ru)")
    print_line("    [" .. keys.key_3.value .. "] - Spanish (es)")
    print_line("     [" .. keys.key_4.value .. "] - Portuguese (pt)")
    print_line("      [" .. keys.key_5.value .. "] - German (de)")
    print_line("       [" .. keys.key_6.value .. "] - Italian (it)")
    
    while LANGUAGE == nil do
        current_input = input.get()
        
        if is_key_released(keys.key_1.value) then
            LANGUAGE = "en"
        elseif is_key_released(keys.key_2.value) then
            LANGUAGE = "ru"
        elseif is_key_released(keys.key_3.value) then
            LANGUAGE = "es"
        elseif is_key_released(keys.key_4.value) then
            LANGUAGE = "pt"
        elseif is_key_released(keys.key_5.value) then
            LANGUAGE = "de"
        elseif is_key_released(keys.key_6.value) then
            LANGUAGE = "it"
        end
        
        emu_frame_advance(5)
    end
    print_separator()
    return LANGUAGE
end

-- ==================== ФУНКЦИИ УТИЛИТЫ ====================

-- Очистка таблиц
function clear_table(t)
    if type(t) ~= "table" then
        debug_log("FAILED clear_table: argument is not a table")
        return
    end
    
    if t then
        for k in pairs(t) do
            t[k] = nil
        end
        debug_log("clear_table: table cleared")
    end
end

-- Чтение байта из ROM
function rom_read_byte(addr)
    if not addr or addr < 0 then
        debug_log(string.format("FAILED rom_read_byte: addr=0x%06X", addr or -1))
        return 0
    end
    
    if rom_size ~= 0 and addr >= rom_size then
        debug_log(string.format("FAILED rom_read_byte: addr=0x%06X rom_size=0x%06X)", 
            addr, rom_size or 0))
        return 0
    end
    
    local success, value = pcall(rom.readbyte, addr)
    if not success then
        debug_log(string.format("FAILED rom_read_byte: addr=0x%06X: %s", 
            addr, tostring(value)))
        return 0
    end
    
    return value
end

-- Чтение знакового байта из ROM
function rom_read_byte_signed(addr)
    if not addr or addr < 0 then
        debug_log(string.format("FAILED rom_read_byte_signed: addr=0x%06X", 
            addr or -1))
        return 0
    end
    
    if rom_size ~= 0 and addr >= rom_size then
        debug_log(string.format("FAILED rom_read_byte_signed: addr=0x%06X rom_size=0x%06X)", 
            addr, rom_size or 0))
        return 0
    end
    
    local success, value = pcall(rom.readbytesigned, addr)
    if not success then
        debug_log(string.format("FAILED rom_read_byte_signed: addr=0x%06X: %s", 
            addr, tostring(value)))
        return 0
    end
    
    return value
end

-- Запись байта в ROM
function rom_write_byte(addr, val)
    if not addr or addr < 0 then
        debug_log(string.format("FAILED rom_write_byte: addr=0x%06X", 
            addr or -1))
        return false
    end
    
    if rom_size ~= 0 and addr >= rom_size then
        debug_log(string.format("FAILED rom_write_byte: addr=0x%06X rom_size=0x%06X)", 
            addr, rom_size or 0))
        return false
    end
    
    if not val then
        debug_log(string.format("FAILED rom_write_byte: addr=0x%06X val=nil", 
            addr))
        return false
    end
    
    -- val = bit.band(val, 0xFF)
    
    local success, err = pcall(rom.writebyte, addr, val)
    if not success then
        debug_log(string.format("FAILED rom_write_byte: addr=0x%06X val=0x%02X: %s", 
            addr, val, tostring(err)))
        return false
    end
    
    return true
end

-- Проверка, является ли опкод инструкций для поиска
function is_necessary_instruction(opcode)
    return instr_table[opcode] ~= nil
end

-- Получение инвертированного значания для опкода
function get_inverted_opcode(opcode)
    local instr = instr_table[opcode]
    return instr and instr[2] or opcode
end

-- Получение имени по опкоду
function get_opcode_name(opcode)
    local instr = instr_table[opcode]
    return instr and instr[1] or string.format("0x%02X", opcode)
end

-- Проверка валидности опкода по кэшированной таблице
function is_valid_nes_instruction(opcode)
    if not opcode then return false end
    return cached_valid_nes_instr[bit.band(opcode, 0xFF)]
end

-- ==================== ФУНКЦИИ ПОИСКА И ОБРАБОТКИ ====================

-- Поиск инструкций в ROM
function find_instructions()
    debug_log("find_instructions: start")
    local start_offset = HEADER_SIZE + trainer_size
    clear_table(cur_state.instructions)
    
    for i = start_offset, rom_size - 2 do
        local first_byte = rom_read_byte(i)
        
        -- Проверяем, есть ли инструкция в таблице поиска
        if is_necessary_instruction(first_byte) then
            -- Опкод ветвления?
			if bit.band(first_byte, 0x1F) == 0x10 then
				-- Читаем знаковое смещение (второй байт инструкции)
				local offset = rom_read_byte_signed(i + 1)
				
				-- Проверяем смещение
				if offset ~= 0 and offset ~= -2 then
					-- Вычисляем адрес перехода
					local jump_addr = i + 2 + offset
					
					-- Проверяем, что адрес перехода находится в пределах ROM
					if jump_addr >= start_offset and jump_addr <= rom_size - 1 then
						-- Проверяем, что следующая инструкция валидна
						local next_byte = rom_read_byte(i + 2)
						if is_valid_nes_instruction(next_byte) then
							-- Проверяем инструкцию по адресу перехода на валидность
							local jump_instruction = rom_read_byte(jump_addr)
							if is_valid_nes_instruction(jump_instruction) then
								-- Сохраняем инструкцию
								table.insert(cur_state.instructions, {
									[INSTR_ADDR_INDEX] = i,
									[INIT_VAL_INDEX] = first_byte
								})
							end
						end
					end
				end
			else
				-- Сохраняем остальные опкоды без проверок
				table.insert(cur_state.instructions, {
					[INSTR_ADDR_INDEX] = i,
					[INIT_VAL_INDEX] = first_byte
				})	
			end
        end
    end
    
    total_instructions = #cur_state.instructions
    debug_log("find_instructions: end, total_instructions=" .. tostring(total_instructions))
    return #cur_state.instructions > 0
end

-- Восстановление оригинальных инструкций в текущем окне
function restore_instructions()
    debug_log("restore_instructions: start")
    for i = cur_state.window_start + 1, math.min(cur_state.window_start + cur_state.window_size, #cur_state.instructions) do
        local instr = cur_state.instructions[i]
        if instr then
            rom_write_byte(instr[INSTR_ADDR_INDEX], instr[INIT_VAL_INDEX])
        end
    end
    debug_log("restore_instructions: end")
end

-- Инвертирование инструкций в текущем окне
function invert_instructions()
    debug_log("invert_instructions: start")
    for i = cur_state.window_start + 1, math.min(cur_state.window_start + cur_state.window_size, #cur_state.instructions) do
        local instr = cur_state.instructions[i]
        if instr then
            rom_write_byte(instr[INSTR_ADDR_INDEX], get_inverted_opcode(instr[INIT_VAL_INDEX]))
        end
    end
    debug_log("invert_instructions: end")
end

-- Перемешивание всех найденных инструкций
function shuffle_instructions()
    debug_log("shuffle_instructions: start")
    if RANDOM_SEED then
        math.randomseed(os.time() * 1000 + emu.framecount())
        debug_log("shuffle_instructions: use random seed")
    end
    
    for i = 1, #cur_state.instructions do
        local j = math.random(1, #cur_state.instructions)
        cur_state.instructions[i], cur_state.instructions[j] = cur_state.instructions[j], cur_state.instructions[i]
    end
    debug_log("shuffle_instructions: end")
end

-- Копирование состояния поиска
function copy_search_state(src, dst)
    debug_log("copy_search_state: start")
    debug_log(string.format("  src instructions: %d", #src.instructions))
    debug_log(string.format("  dst instructions before: %d", #dst.instructions))
    
    if not src or not src.instructions then 
        debug_log("FAILED copy_search_state: empty src state")
        return 
    end
    
    for k in pairs(dst) do
        dst[k] = nil
    end
    
    for key, value in pairs(src) do
        if key ~= "instructions" then
            dst[key] = value
        end
    end
    
    dst.instructions = {}
    for i, instr in ipairs(src.instructions) do
        dst.instructions[i] = {
            [INSTR_ADDR_INDEX] = instr[INSTR_ADDR_INDEX],
            [INIT_VAL_INDEX] = instr[INIT_VAL_INDEX]
        }
    end
    debug_log(string.format("  dst instructions after: %d", #dst.instructions))
    debug_log("copy_search_state: end")
end

-- Проверка наличия инструкций в состоянии поиска
function has_search_state(state)
    return state and state.instructions and #state.instructions > 0
end

-- ==================== ОБРАБОТКА ШАГОВ ПОИСКА ====================

-- Шаг 1: Баг мешает (пропускаем текущее окно)
function process_step1()
    copy_search_state(cur_state, prev_state)
    restore_instructions()
    
    if cur_state.window_start + cur_state.window_size < #cur_state.instructions then
        cur_state.window_start = cur_state.window_start + cur_state.window_size
    else
        if cur_state.window_size > 1 then
            cur_state.window_start = 0
            cur_state.window_size = math.floor(cur_state.window_size / 2)
            if not cur_state.search_localizing then
                shuffle_instructions()
            end
        else
            return false
        end
    end
    
    return true
end

-- Шаг 2: Нет изменения (удаляем текущее окно)
function process_step2()
    copy_search_state(cur_state, prev_state)
    restore_instructions()
    
    if cur_state.window_start + cur_state.window_size < #cur_state.instructions then
        for i = 1, cur_state.window_size do
            table.remove(cur_state.instructions, cur_state.window_start + 1)
        end
    else
        if cur_state.window_size > 1 and cur_state.window_start ~= 0 then
            for i = #cur_state.instructions, cur_state.window_start + 1, -1 do
                table.remove(cur_state.instructions, i)
            end
            cur_state.window_start = 0
            cur_state.window_size = math.floor(cur_state.window_size / 2)
            if not cur_state.search_localizing then
                shuffle_instructions()
            end
        else
            return false
        end
    end
    
    return true
end

-- Шаг 3: Есть изменение (сужаем область поиска)
function process_step3()
    copy_search_state(cur_state, prev_state)
    
    if not cur_state.search_localizing then
        copy_search_state(cur_state, pre_local_state)
        cur_state.search_localizing = true
    end
    
    if cur_state.window_size > 1 and #cur_state.instructions > 1 then
        restore_instructions()
        
        for i = cur_state.window_start, 1, -1 do
            table.remove(cur_state.instructions, 1)
        end
        cur_state.window_start = 0
        
        if cur_state.window_size < #cur_state.instructions then
            for i = #cur_state.instructions, cur_state.window_size + 1, -1 do
                table.remove(cur_state.instructions, i)
            end
        end
        
        cur_state.window_size = math.floor(cur_state.window_size / 2)
    else
        -- Найдена инструкция
        if has_search_state(cur_state)
                    and cur_state.window_start + 1 <= #cur_state.instructions then
            for i = #cur_state.instructions, 2, -1 do
                table.remove(cur_state.instructions, i)
            end
            
            cur_state.search_done = true
            cur_state.search_active = false
            cur_state.search_localizing = false
        else
            return false
        end
    end
            
    return true
end

-- ==================== ФУНКЦИИ ВЫВОДА ====================

-- Вывод отладочной информации в файл
function debug_log(msg)
    if DEBUG_MODE then
        local f = io.open(LOG_FILE, "a")
        if f then
            f:write(string.format("[%s][%06d] %s\n",
                        os.date("%H:%M:%S"), emu.framecount(), msg))
            f:close()
        end
    end
end

-- Вывод строки в консоль
function print_line(msg)
    debug_log("   @: " .. msg)
    emu.print(convert_encoding(msg, LANGUAGE))
end

-- Разделитель с движущимся процентом по шкале
function print_separator()
    local length = 38
    print_line("")
    
    if total_instructions > 0 and not cur_state.search_done then
        local progress = (total_instructions - #cur_state.instructions) / total_instructions
        local percent_text = string.format("%2d%%", math.floor(progress * 100))
        local pos = math.floor(progress * (length - #percent_text + 1))
        
        print_line(("="):rep(pos) .. percent_text
                        .. ("="):rep(length - pos - #percent_text))
    else
        print_line(("="):rep(length))
    end
    
    print_line("")
end

-- Вывод сообщения об ошибке
function print_error(msg)
    print_separator()
    print_line(string.format("   [%s: %s]", tr("err"), msg))
end

-- Вывод сообщения о выбранном действии
function print_action(msg)
    print_separator()
    print_line(string.format("   [%s: %s]", tr("action"), msg))
end

-- Начальное меню
function menu_start()
    -- Сброс переменных и таблиц
    rom_hash = nil
    total_instructions = 0
    cur_state.search_active = false
    cur_state.search_done = false
    cur_state.search_fail = false
    clear_table(cur_state.instructions)
    clear_table(prev_state.instructions)
    clear_table(pre_local_state.instructions)
    instr_select_mode = false
    instr_select_cursor = 1
    
    -- Восстанавливаем инструкции из оригинальной таблицы
    for k, v in pairs(init_instr_table) do
        instr_table[k] = v
    end
    
    update_active_instructions()
    
    if DEBUG_MODE then
        print_separator()
        print_line("   [DEBUG_MODE ON]")
    end
    print_separator()
    print_line("--- ROM Glitcher: II v" .. SCRIPT_VERSION 
                                .. " (FCEUX " .. FCEUX_MIN_VERSION .. "+) ---")
    print_line("  " .. tr("detected") .. " "
                .. (qt_version and "Qt" or tr("non_qt")).. " " .. tr("version"))
    print_line("")
    
    local all_instructions = {}
    for _, data in pairs(init_instr_table) do
        if data and data[1] then
            table.insert(all_instructions, data[1])
        end
    end
    table.sort(all_instructions)
    
    print_line(tr("available_instructions") .. ":")
    print_line("  " .. table.concat(all_instructions, ", "))
    print_line("")
    print_line(tr("selected_instructions") .. ":")
    if next(active_instr_groups) ~= nil then
        local selected_instructions = {}
        for _, data in pairs(instr_table) do
            if data and data[1] then
                table.insert(selected_instructions, data[1])
            end
        end
        table.sort(selected_instructions)
        if #selected_instructions > 0 then
            print_line("  " .. table.concat(selected_instructions, ", "))
        else
            print_line("  (" .. tr("nothing_selected") .. ")")
        end
    else
        print_line("  (" .. tr("nothing_selected") .. ")")
    end
    print_line("")
    print_line("1. " .. tr("load_rom"))
    print_line(string.format(" 2. " .. tr("press_to_select"), keys.key_5.value))
    print_line("  3. " .. tr("reach_point"))
    print_line(string.format("   4. " .. tr("press_to_start"), keys.key_6.value))
end

-- Меню выбора инструкций
function menu_select()
    print_separator()
    print_line("--- " .. tr("instruction_selection") .. " ---")
    print_line("")
    
    local types = collect_instruction_types()
    
    for i, type_name in ipairs(types) do
        local examples = {}
        for _, data in pairs(init_instr_table) do
            if data and data[3] == type_name then
                if data[1] then
                    table.insert(examples, data[1])
                end
            end
        end
        
        -- Курсор и метка
        local cursor = (i == instr_select_cursor) and ">" or "     "
        local checkbox = active_instr_groups[type_name] and "[X]" or "[ ]"
        
        if #examples > 0 then table.sort(examples) end
        
        print_line(string.format("%s %s   %d. %s",
                                cursor, checkbox, i, table.concat(examples, ", ")))
    end
    
    print_line("")
    print_line(tr("controls") .. ":")
    print_line(" [" .. keys.key_1.value .. "] - " .. keys.key_1.desc_select)
    print_line("  [" .. keys.key_2.value .. "] - " .. keys.key_2.desc_select)
    print_line("   [" .. keys.key_3.value .. "] - " .. keys.key_3.desc_select)
    print_line("    [" .. keys.key_4.value .. "] - " .. keys.key_4.desc_select)
    print_line("")
    print_line("     [" .. keys.key_5.value .. "] - " .. keys.key_5.desc_select)
end

-- Меню поиска
function menu_search()
    print_separator()
    print_line("--- " .. tr("search_status") .. " ---")
    print_line(tr("instruction_count") .. ": " .. #cur_state.instructions)
    print_line(tr("step") .. ": " .. cur_state.step 
                    .. (cur_state.search_localizing and " | " .. tr("localization") or ""))
    print_line(tr("window") .. ": " .. cur_state.window_start .. "-" .. 
        math.min(cur_state.window_start + cur_state.window_size, #cur_state.instructions) .. 
        " | " .. tr("size") .. ": " .. cur_state.window_size)
    print_line("")
    print_line(tr("controls") .. ":")
    print_line(" [" .. keys.key_1.value .. "] - " .. keys.key_1.desc_search)
    print_line("  [" .. keys.key_2.value .. "] - " .. keys.key_2.desc_search)
    print_line("   [" .. keys.key_3.value .. "] - " .. keys.key_3.desc_search)
    if has_search_state(prev_state) then
        print_line("    [" .. keys.key_4.value .. "] - " .. keys.key_4.desc_search)
    end
    print_line("")
    if has_search_state(pre_local_state) then
        print_line("  [" .. keys.key_5.value .. "] - " .. keys.key_5.desc_search)
    end
    print_line(" [" .. keys.key_6.value .. "] - " .. keys.key_6.desc_search)
end

-- Меню завершения поиска
function menu_end_search()
    print_separator()
    print_line(" [" .. keys.key_6.value .. "] - " .. keys.key_6.desc_select)
    if has_search_state(pre_local_state) then
        print_line("  [" .. keys.key_5.value .. "] - "
                            .. tr("continue_from") .. " " .. keys.key_5.desc_search)
    end
    if cur_state.search_done and not cur_state.search_fail then
        print_line("   [" .. keys.key_7.value .. "] - " .. keys.key_7.desc_search)
    end
end

-- ==================== ФУНКЦИИ ВЫБОРА ИНСТРУКЦИЙ ====================

-- Собираем типы инструкций из оригинальной таблицы
function collect_instruction_types()
    debug_log("collect_instruction_types: start")
    local types = {}
    for _, data in pairs(init_instr_table) do
        if data and data[3] then
            types[data[3]] = true
        end
    end
    
    available_instr_groups = {}
    for type_name, _ in pairs(types) do
        table.insert(available_instr_groups, type_name)
    end
    table.sort(available_instr_groups)
    debug_log("collect_instruction_types: end")
    
    return available_instr_groups
end

-- Обновляем активные инструкции на основе отмеченныx
function update_active_instructions()
    debug_log("update_active_instructions: start")
    local temp_table = {}
    
    -- Выбираем только отмеченные инструкции 
    if next(active_instr_groups) ~= nil then
        for opcode, data in pairs(init_instr_table) do
            if data and data[3] and active_instr_groups[data[3]] then
                temp_table[opcode] = data
            end
        end
    end
    
    instr_table = temp_table
    debug_log("update_active_instructions: end")
    
    return next(temp_table) ~= nil
end

-- ==================== ФУНКЦИИ РАБОТЫ С КОНФИГУРАЦИЕЙ ====================

-- Функция для создания маппинга конфиг-ключей
local function create_key_mapping()
    debug_log("create_key_mapping: start")
    local mapping = {}
    for key_name, key_data in pairs(keys) do
        local config_key = key_name:lower()  -- key_1 -> key_1
        mapping[config_key] = key_name
    end
    debug_log("create_key_mapping: end")
    return mapping
end

-- Сохранение конфигурации в файл
function config_save()
    debug_log("config_save: start")
    
    local success, file = pcall(io.open, CONFIG_FILE, "w")
    if not success or not file then
        debug_log("FAILED config_save: not success or not file")
        return false
    end
    
    file:write("# FCEUX ROM Glitcher v" .. SCRIPT_VERSION .. " " .. tr("config_file") .. "\n\n")
    file:write("# " .. tr("available_langs") .. ": en, ru, es, pt, de, it\n")
    file:write("language=" .. LANGUAGE .. "\n\n")
    local types = collect_instruction_types()
    file:write("# " .. tr("selected_groups_desc") .. "\n")
    file:write("# " .. tr("available_groups_list") .. ": "
                               .. (#types > 0 and table.concat(types, ", ") or "") .. "\n")
    if next(active_instr_groups) == nil then
        file:write("instruction_groups=none\n\n")
    else
        local groups = {}
        for type_name, _ in pairs(active_instr_groups) do
            table.insert(groups, type_name)
        end
        table.sort(groups)
        file:write(string.format("instruction_groups=%s\n\n", table.concat(groups, ",")))
    end
    
    file:write("# " .. tr("save_mod_path_desc") .. "\n")
    file:write(string.format("save_mod_path=%s\n\n", SAVE_MOD_PATH))
    
    file:write("# " .. tr("key_bindings") .. "\n")
    local key_mapping = create_key_mapping()
    local sorted_keys = {}
    
    for config_key, _ in pairs(key_mapping) do
        table.insert(sorted_keys, config_key)
    end
    table.sort(sorted_keys)
    
    for _, config_key in ipairs(sorted_keys) do
        local key_name = key_mapping[config_key]
        local key_data = keys[key_name]
        file:write(string.format("#    %s | %s\n", key_data.desc_search, key_data.desc_select))
        file:write(string.format("%s=%s\n", config_key, key_data.value))
    end
    file:write("\n")
    
    file:write("# " .. tr("available_keys") .. ":\n")
    file:write("#    leftclick, rightclick, middleclick, capslock, numlock, scrolllock,\n")
    file:write("#    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,\n")
    file:write("#    A, B, C, ..., Y, Z,\n")
    file:write("#    F1, F2, F3, ..., F23, F24,\n")
    file:write("#    backspace, tab, enter, shift, control, alt, pause,\n")
    file:write("#    escape, space, pageup, pagedown, end, home, \n")
    file:write("#    left, up, right, down, \n")
    file:write("#    numpad0, numpad1, numpad2, ..., numpad8, numpad9, \n")
    file:write("#    numpad*, insert, delete, numpad+, numpad-, numpad., numpad/, semicolon, plus, minus, \n")
    file:write("#    comma, period, slash, backslash, tilde, quote, leftbracket, rightbracket.\n\n")
    
    file:write("# " .. tr("window_size_desc") .. "\n")
    file:write(string.format("start_length_div=%d\n\n", START_LENGTH_DIV))
    file:write("# " .. tr("random_seed_desc") .. "\n")
    file:write(string.format("random_seed=%d\n\n", RANDOM_SEED and 1 or 0))
    file:write("# " .. tr("debug_mode_desc") .. "\n")
    file:write(string.format("debug_mode=%d\n\n", DEBUG_MODE and 1 or 0))
    
    file:close()
    debug_log("config_save: end")
    return true
end

-- Загрузка конфигурации из файла
function config_load()
    debug_log("config_load: start")
    local success, file = pcall(io.open, CONFIG_FILE, "r")
    if not success or not file then
        debug_log("FAILED config_load: not success or not file")
        
        -- Запрос и загрузка языка интерфейса
        lang_load(lang_ask())
        
        -- Создаем конфиг, если файл отсутствует
        collect_instruction_types()
        
        local found_default = false
        for _, type_name in ipairs(available_instr_groups) do
            if type_name == DEFAULT_GROUP then
                active_instr_groups[type_name] = true
                found_default = true
                break
            end
        end
        
        if not found_default then
            if #available_instr_groups > 0 then
                active_instr_groups[available_instr_groups[1]] = true
            end
        end
        
        update_active_instructions()
        
        if config_save() then
            success, file = pcall(io.open, CONFIG_FILE, "r")
            if not success or not file then
                debug_log("FAILED config_load: again not success or not file")
                return false
            end
            print_line(CONFIG_FILE .. " " .. tr("created_in_folder"))
        else
            return false
        end
    end
    
    active_instr_groups = {}
    
    for line in file:lines() do
        -- Очищаем строку от начальных и конечных пробелов
        line = line:match("^%s*(.-)%s*$")
        
        -- Пропускаем пустые строки и комментарии
        if line ~= "" and line:sub(1, 1) ~= "#" then
            local key, value = line:match("^([^=]+)=(.+)$")
            if key and value then
                key = key:match("^%s*(.-)%s*$")
                value = value:match("^%s*(.-)%s*$")
                
                if key == "language" then
                    LANGUAGE = value
                
                elseif key == "instruction_groups" then
                    if value ~= "none" then
                        for type_name in value:gmatch("[^,]+") do
                            type_name = type_name:match("^%s*(.-)%s*$")
                            if type_name ~= "" then
                                active_instr_groups[type_name] = true
                            end
                        end
                    end
                
                elseif key == "save_mod_path" then
                    SAVE_MOD_PATH = value
                
                elseif key == "start_length_div" then
                    START_LENGTH_DIV = tonumber(value) or START_LENGTH_DIV
                
                elseif key == "random_seed" then
                    local num = tonumber(value)
                    if num == 1 then RANDOM_SEED = true
                    elseif num == 0 then RANDOM_SEED = false
                    end
                    
                elseif key == "debug_mode" then
                    local num = tonumber(value)
                    if num == 1 then DEBUG_MODE = true
                    elseif num == 0 then DEBUG_MODE = false
                    end
    
                else  -- Клавиши управления
                    local key_mapping = create_key_mapping()
                    if key_mapping[key] then
                        keys[key_mapping[key]].value = value
                    end
                end
            end
        end
    end
    
    file:close()
    
    -- Загрузка языка интерфейса
    lang_load(LANGUAGE)
    
    -- Инициализируем состояния клавиш
    key_states = {}
    for _, key_data in pairs(keys) do
        key_states[key_data.value] = false
    end
    
    -- Если не выбрано ни одной группы, выбираем группу по умолчанию
    if next(active_instr_groups) == nil then
        active_instr_groups[DEFAULT_GROUP] = true
    end
    
    debug_log("config_load: end")
    return true
end

-- ==================== ОСНОВНЫЕ ФУНКЦИИ ====================
-- Эмуляция на num_frames кадров вперёд
function emu_frame_advance(num_frames)
    for i = 1, num_frames do
        emu.frameadvance()
    end
end

-- Сохранение состояния игры
function savestate_save()
    debug_log("savestate_save: start")
    if not temp_savestate then 
        debug_log("FAILED savestate_save: not temp_savestate")
        return false 
    end

    savestate.save(temp_savestate)
    savestate.persist(temp_savestate)
    emu_frame_advance(5)
    debug_log("savestate_save: end")
    
    return true
end

-- Загрузка состояния игры
function savestate_load()
    debug_log("savestate_load: start")
    if not temp_savestate then 
        debug_log("FAILED savestate_load: not temp_savestate")
        return false 
    end

    savestate.load(temp_savestate)
    emu_frame_advance(5)
    debug_log("savestate_load: end")
    return true
end

-- Сброс игры
function emu_soft_reset()
    debug_log("emu_soft_reset: start")
    -- emu.poweron()
    emu.softreset()
    emu_frame_advance(5)
    debug_log("emu_soft_reset: end")
end

-- Начало нового поиска
function new_search()
    print_separator()
    print_line("--- " .. tr("new_search") .. " ---")
    
    if not emu.emulating() then
        debug_log("FAILED new_search: emulation not active")
        print_error(tr("error_emulation"))
        return false
    end
    
    -- Проверяем сигнатуру NES (NES\x1A)
    if rom_read_byte(0) ~= 0x4E or rom_read_byte(1) ~= 0x45 or 
       rom_read_byte(2) ~= 0x53 or rom_read_byte(3) ~= 0x1A then
        print_error(tr("error_nes_header"))
        return false
    end
    
    -- Определяем размер ROM
    local prg_rom_size = rom_read_byte(4) * 16384  -- PRG ROM (16KB блоки)
    local chr_rom_size = rom_read_byte(5) * 8192   -- CHR ROM (8KB блоки)
    local flags6 = rom_read_byte(6)
    trainer_size = (bit.band(flags6, 0x04) ~= 0) and 512 or 0
    rom_size = HEADER_SIZE + trainer_size + prg_rom_size + chr_rom_size
    
    rom_filename = rom.getfilename()
    check_rom_hash()
    print_line("ROM: " .. rom_filename)
    print_line("Hash MD5: " .. rom_hash)
    print_line(string.format(tr("rom_size"), rom_size / 1024, rom_size))
    print_line("Seed: " .. (RANDOM_SEED and tr("seed_random") or tr("seed_fixed")))
    print_line("Backup ROM: " .. (create_rom_backup() and "OK" or tr("err")))
    print_line("Savestate: " .. (savestate_save() and "OK" or tr("err")))
    update_active_instructions()
    
    if next(active_instr_groups) ~= nil then
        local selected = {}
        for type_name, _ in pairs(active_instr_groups) do
            table.insert(selected, type_name:upper())
        end
        table.sort(selected)
        print_line(tr("selected_types") .. ": " .. table.concat(selected, ", "))
    else
        print_error(tr("error_no_groups"))
        return false
    end
    
    -- Ищем инструкции
    if find_instructions() then
        print_line(tr("instructions_found") .. ": " .. #cur_state.instructions)
    else
        print_error(tr("error_no_instructions"))
        return false
    end
    
    debug_log("new_search: instructions found=" .. tostring(#cur_state.instructions))
    
    if DEBUG_MODE then
        print_line("")
        print_line("   [DEBUG_MODE ON]")
    end
    
    -- Инициализируем поиск
    shuffle_instructions()
    cur_state.window_start = 0
    cur_state.window_size = math.floor(#cur_state.instructions / START_LENGTH_DIV) + 
                          (#cur_state.instructions % START_LENGTH_DIV > 0 and 1 or 0)
    cur_state.step = 1
    cur_state.search_localizing = false
    cur_state.search_done = false
    cur_state.search_fail = false
    cur_state.search_active = true
    
    -- Очищаем предыдущие состояния
    clear_table(prev_state.instructions)
    clear_table(pre_local_state.instructions)
    
    -- Применяем инвертирование и загружаем состояние
    invert_instructions()
    -- emu_soft_reset()
    savestate_load()
    menu_search()
    
    return true
end

-- Сохранение бэкапа ROM
function create_rom_backup()
    debug_log("create_rom_backup: start, rom_size=" .. tostring(rom_size))
    rom_backup = {}
    for addr = HEADER_SIZE, rom_size - 1 do
        rom_backup[addr] = rom_read_byte(addr)
    end
    
    if not rom_backup or type(rom_backup) ~= "table" or not next(rom_backup) then
        debug_log("FAILED create_rom_backup: rom_backup not create")
        return false
    end
    
    
    if DEBUG_MODE then
        local backup_count = 0
        for _ in pairs(rom_backup) do
            backup_count = backup_count + 1
        end
        debug_log(string.format("create_rom_backup: end, backup_elements=%d, expected=%d %s", 
            backup_count, rom_size - HEADER_SIZE, 
            (backup_count == rom_size - HEADER_SIZE and "OK" or "FAIL")))
    end
    return true
end

-- Восстановление бэкапа ROM
function restore_rom_backup()
    debug_log("restore_rom_backup: start")
    if not rom_backup or type(rom_backup) ~= "table" or not next(rom_backup) then
        print_error(tr("error_backup"))
        return false
    end
    
    for addr, val in pairs(rom_backup) do
        rom_write_byte(addr, val)
    end
    debug_log("restore_rom_backup: end")
    return true
end

-- Сохранение модифицированного ROM
function save_mod_rom()
    debug_log("restore_rom_backup: start")
    if not has_search_state(cur_state) then 
        print_error(tr("error_no_changes"))
        return false 
    end
    
    if not rom_backup then
        print_error(tr("error_backup"))
        return false
    end
    
    -- Создаем временную таблицу для быстрого поиска изменений
    local modify_instr = {}
    local first_instr_addr = nil
    local first_instr_init_val = nil
    local first_instr_inver_val = nil
    
    for _, instr in ipairs(cur_state.instructions) do
        local addr = instr[INSTR_ADDR_INDEX]
        if addr >= 0 and addr < rom_size then
            modify_instr[addr] = get_inverted_opcode(instr[INIT_VAL_INDEX])
            
            if not first_instr_addr then
                first_instr_addr = addr
                first_instr_init_val = instr[INIT_VAL_INDEX]
                first_instr_inver_val = modify_instr[addr]
            end
        end
    end
    
    if not first_instr_addr then
        print_error(tr("error_no_changes"))
        return false
    end
    
    local file_counter = 0
    local full_path
    local file_exists
    
    repeat
        local filename = string.format("%s_%06X_%02Xto%02X%s.nes", rom_filename, 
                            first_instr_addr, first_instr_init_val, first_instr_inver_val,
                            file_counter > 0 and "(" .. file_counter .. ")" or "")
        full_path = SAVE_MOD_PATH
                    .. (SAVE_MOD_PATH ~= "" and (emu.getdir() or ""):sub(-1) or "")
                    .. filename
        
        local success, exists = pcall(function()
            local test_file = io.open(full_path, "r")
            if test_file then
                test_file:close()
                return true
            end
            return false
        end)
        
        file_exists = success and exists
        file_counter = file_counter + 1
    until not file_exists
    
    -- Сохраняем файл
    local save_success, save_error = pcall(function()
        local file, err = io.open(full_path, "wb")
        if not file then
            print_error(tr("error_save_rom") .. ": " .. full_path .. " - " .. (err or tr("err")))
        end
        
        -- Записываем заголовок (первые HEADER_SIZE байт) напрямую из памяти
        for i = 0, HEADER_SIZE - 1 do
            local byte = rom_read_byte(i)
            local write_success, write_err = pcall(function()
                return file:write(string.char(byte))
            end)
            if not write_success then
                print_error(tr("error_write_header") .. ": " .. (write_err or tr("err")))
            end
        end
        
        -- Записываем остальные байты из резервной копии, применяя изменения
        for addr = HEADER_SIZE, rom_size - 1 do
            local byte = rom_backup[addr]  -- Берем байт из резервной копии
            
            if modify_instr[addr] then
                byte = modify_instr[addr]
            end
            
            local write_success, write_err = pcall(function()
                return file:write(string.char(byte))
            end)
            if not write_success then
                print_error(tr("error_write_address") .. " "
                                    .. addr .. ": " .. (write_err or tr("err")))
            end
        end
        
        file:close()
        return true
    end)
    
    if not save_success then
        print_error(save_error)
        return false
    end
    
    print_separator()
    print_line(tr("saved_to") .. (SAVE_MOD_PATH == "" and " " .. tr("script_folder") or "")
                                        .. ": " .. full_path)
    debug_log("restore_rom_backup: end")
    return true
end

function check_rom_hash()
    local current_hash = rom.gethash("md5")
    
    if not rom_hash then
        rom_hash = current_hash
        return true
    end
    
    if current_hash ~= rom_hash then return false end
    
    return true
end

-- ==================== ОБРАБОТКА ВВОДА ====================
-- Проверка нажатия клавиши
function is_key_pressed(key_name)
    local cur_key_state = current_input[key_name] or false
    local prev_key_state = key_states[key_name] or false
    
    if cur_key_state and not prev_key_state then
        key_states[key_name] = true
        debug_log("is_key_pressed: key=" .. tostring(key_name))
        return true
    elseif not cur_key_state and prev_key_state then
        key_states[key_name] = false
    end
    return false
end

-- Проверка отпускания клавиши
function is_key_released(key_name)
    local cur_key_state = current_input[key_name] or false
    local prev_key_state = key_states[key_name] or false
    
    if not cur_key_state and prev_key_state then
        key_states[key_name] = false
        debug_log("is_key_released: key=" .. tostring(key_name))
        return true
    elseif cur_key_state and not prev_key_state then
        key_states[key_name] = true
    end
    
    return false
end

-- Обработка ввода
function process_input()
    current_input = input.get()
    
    -- Если активен режим выбора групп
    if instr_select_mode then
        -- Курсор вверх
        if is_key_released(keys.key_1.value) then
            local types = collect_instruction_types()
            if #types > 0 then
                instr_select_cursor = instr_select_cursor - 1
                if instr_select_cursor < 1 then
                    instr_select_cursor = #types
                end
                menu_select()
            end
            return
        end
        
        -- Выбрать/снять текущую группу
        if is_key_released(keys.key_2.value) then
            local types = collect_instruction_types()
            if instr_select_cursor >= 1 and instr_select_cursor <= #types then
                if active_instr_groups[types[instr_select_cursor]] then
                    active_instr_groups[types[instr_select_cursor]] = nil
                else
                    active_instr_groups[types[instr_select_cursor]] = true
                end
                update_active_instructions()
                menu_select()
            end
            return
        end
        
        -- Курсор вниз
        if is_key_released(keys.key_3.value) then
            local types = collect_instruction_types()
            if #types > 0 then
                instr_select_cursor = instr_select_cursor + 1
                if instr_select_cursor > #types then
                    instr_select_cursor = 1
                end
                menu_select()
            end
            return
        end
        
        -- Выбрать все инструкции
        if is_key_released(keys.key_4.value) then
            local types = collect_instruction_types()
            local all_selected = true
            for _, type_name in ipairs(types) do
                if not active_instr_groups[type_name] then
                    all_selected = false
                    break
                end
            end
            
            for _, type_name in ipairs(types) do
                if all_selected then
                    active_instr_groups[type_name] = nil
                else
                    active_instr_groups[type_name] = true
                end
            end
            
            update_active_instructions()
            menu_select()
            return
        end
        
        -- Выйти назад в главное меню
        if is_key_released(keys.key_5.value) then
            print_action(tr("back_to_main"))
            instr_select_mode = false
            
            -- Обновляем активные инструкции и сохраняем конфигурацию
            if update_active_instructions() then
                if not config_save() then
                    print_error(tr("error_save_config"))
                end
            else
                print_error(tr("no_groups"))
            end
            menu_start()
            
            return
        end
        
        return
    end
    
    -- Новый поиск
    if is_key_released(keys.key_6.value) and cur_state then
        if cur_state.search_active or cur_state.search_done
                or cur_state.search_fail then
            print_action(tr("search_complete"))
            restore_rom_backup()
            emu_soft_reset()
            menu_start()
        else
            print_action(tr("search_start"))
            if not new_search() then
                menu_start()
            end
        end
        
        return
    end
    
    -- Шаг до локализации / Выбор инструкций / Назад
    if is_key_released(keys.key_5.value) and cur_state then
        if not cur_state.search_active and not cur_state.search_done
                and not cur_state.search_fail then
            print_action(tr("selecting_instructions"))
            instr_select_mode = true
            -- instr_select_cursor = 1
            menu_select()
            return
        elseif has_search_state(pre_local_state) then
            print_action(keys.key_5.desc_search)
            restore_instructions()
            copy_search_state(pre_local_state, cur_state)
            clear_table(pre_local_state.instructions)
            invert_instructions()
            -- emu_soft_reset()
            savestate_load()
            menu_search()
            return
        end
    end
    
    -- Сохранение ROM
    if is_key_released(keys.key_7.value) and cur_state
            and cur_state.search_done
            and not cur_state.search_fail then
        print_action(keys.key_7.desc_search)
        save_mod_rom()
        -- emu_soft_reset()
        savestate_load()
        menu_end_search()
        return
    end
    
    -- Отмена шага
    if is_key_released(keys.key_4.value) 
            and has_search_state(prev_state) then
        print_action(keys.key_4.desc_search)
        restore_instructions()
        copy_search_state(prev_state, cur_state)
        clear_table(prev_state.instructions)
        invert_instructions()
        -- emu_soft_reset()
        savestate_load()
        menu_search()
        return
    end
    
    -- Обработка шагов поиска только если поиск активен
    if not cur_state.search_active then return end
    
    -- Шаг 1: Баг мешает
    if is_key_released(keys.key_1.value) then
        if process_step1() then
            print_action(keys.key_1.desc_search)
            invert_instructions()
            -- emu_soft_reset()
            savestate_load()
            cur_state.step = cur_state.step + 1
            menu_search()
        else
            print_separator()
            print_line("   [" .. tr("search_failed") .. "]")
            cur_state.search_active = false
            cur_state.search_fail = true
            menu_end_search()
        end
        
        return
    end
    
    -- Шаг 2: Нет изменения
    if is_key_released(keys.key_2.value) then
        if process_step2() then
            print_action(keys.key_2.desc_search)
            invert_instructions()
            -- emu_soft_reset()
            savestate_load()
            cur_state.step = cur_state.step + 1
            menu_search()
        else
            print_separator()
            print_line("   [" .. tr("search_failed") .. "]")
            cur_state.search_active = false
            cur_state.search_fail = true
            menu_end_search()
        end
        
        return
    end
    
    -- Шаг 3: Есть изменение
    if is_key_released(keys.key_3.value) then
        if process_step3() then
            if not cur_state.search_done then
                print_action(keys.key_3.desc_search)
                invert_instructions()
                -- emu_soft_reset()
                savestate_load()
                cur_state.step = cur_state.step + 1
                menu_search()
            else
                -- Выводим информацию о найденной инструкции
                local instr = cur_state.instructions[cur_state.window_start + 1]
                local addr = instr[INSTR_ADDR_INDEX]
                local old_value = instr[INIT_VAL_INDEX]
                local new_value = get_inverted_opcode(old_value)
                print_separator()
                print_line(string.format(" " .. tr("instruction_found") .. ": 0x%06X", addr))
                print_line(string.format("  %s (0x%X) -> %s (0x%X)", 
                                    get_opcode_name(old_value), old_value,
                                    get_opcode_name(new_value), new_value))
                menu_end_search()
            end
        else
            print_separator()
            print_line("   [" .. tr("search_failed") .. "]")
            cur_state.search_active = false
            cur_state.search_fail = true
            menu_end_search()
        end
        
        return
    end
end

-- ==================== ИНИЦИАЛИЗАЦИЯ ====================
-- Восстановление памяти и очистка при выходе
function end_script()
    debug_log("end_script: start")
    
    clear_table(cur_state.instructions)
    clear_table(prev_state.instructions)
    clear_table(pre_local_state.instructions)
    clear_table(key_states)
    clear_table(current_input)
    
    if emu.emulating() then
        debug_log("end_script: emu.emulating=true")
        restore_rom_backup()
        
        local success, err = pcall(function()
            emu.softreset()
        end)
        if not success then
            print_error(tr("error_soft_reset") .. " Soft reset " .. err)
        end
    end
    rom_backup = nil
    
    collectgarbage("collect")
    total_instructions = 0
    print_separator()
    print_line("   [" .. tr("script_completed") .. "]")
    emu.registerexit(nil)
    debug_log("end_script: end")
end

-- ==================== ОСНОВНОЙ ЦИКЛ ====================
function main_loop()
    -- Проверка на отсутствие эмуляции
    if not emu.emulating() then
        print_error(tr("error_rom_load"))
    else
        -- Проверка смены ROM-файла каждый N кадр
        if emu.framecount() % 60 == 0 then
            if not check_rom_hash() then
                print_error(tr("error_rom_changed"))
                menu_start()
            end
        end
    end
    
    process_input()
end

-- ==================== ЗАПУСК СКРИПТА ====================
-- Определение Qt/не-Qt версии по наличию папки "bin" в пути к исполняемому файлу
qt_version = (emu.getdir() or ""):lower():find("[\\/]bin[\\/]") ~= nil

-- Сохраняем оригинальную таблицу инструкций для выборки типов
for k, v in pairs(instr_table) do
    init_instr_table[k] = v
end

-- Создаём таблицу состояния клавиш
for _, key_data in pairs(keys) do
    key_states[key_data.value] = false
end

-- Чтение параметров из cfg-файла и загрузка локализации интерфейса
config_load()

-- Начало новой сессии в log-файле
if DEBUG_MODE then
    debug_log(("\n"):rep(3) .. ("#"):rep(70) .. " -NEW LOG- #####")
    debug_log("Script v" .. SCRIPT_VERSION .. ", FCEUX "
            .. (qt_version and "Qt" or "Non-Qt") ..  " version")
end

-- В FCEUX 2.2.3 отсутствует функция получения имени загруженного ROM
if type(rom.getfilename) ~= "function" then
    rom.getfilename = function()
        return "GAME_ROM" end
    debug_log("Function rom.getfilename() not found, return " .. rom.getfilename())
end

-- В FCEUX 2.2.3 функция получение хэш суммы ROM отсутствует в описании, но работает
if type(rom.gethash) ~= "function" then
    rom.gethash = function(type)
        return "######## EMPTY ######## EMPTY ##"
    end
    debug_log("Function rom.gethash() not found, return " .. rom.gethash())
end

-- Создание кэшированной таблицы валидных опкодов
do
    local validation_table = {
        0xc6, 0xe6, 0xc6, 0xc6, 0xce, 0xee, 0xc6, 0xc6,
        0xc6, 0xee, 0xc6, 0xc6, 0xc6, 0xee, 0xc6, 0xc6,
        0x4e, 0xae, 0xce, 0xe4, 0xee, 0xee, 0xce, 0xee,
        0xce, 0xee, 0xc6, 0xc6, 0xce, 0xee, 0xc6, 0xc6
    }
    
    for i = 0, 255 do
        local idx = math.floor(i / 8) + 1
        local bit_pos = 7 - (i % 8)
        local byte = validation_table[idx]
        cached_valid_nes_instr[i] = bit.band(bit.rshift(byte, bit_pos), 1) == 1
    end
    
    local valid_count = 0
    for _, v in pairs(cached_valid_nes_instr) do
        if v then valid_count = valid_count + 1 end
    end
    debug_log(string.format("Cached valid opcode: %d/256 %s", valid_count, 
                    (valid_count == 151 and "OK" or "ERROR")))
end

-- Контейнер для хранения состояния игры
temp_savestate = savestate.object()

menu_start()
emu.registerexit(end_script)  -- Регистрация обработчика завершения скрипта

while true do  -- loop
    main_loop()
    emu_frame_advance(1)
end