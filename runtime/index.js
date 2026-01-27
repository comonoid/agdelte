/**
 * Agdelte Runtime - Main Entry Point
 * Запускает Elm-подобное приложение в браузере
 */

import { createElement, patch } from './dom.js';
import { interpretEvent, unsubscribe } from './events.js';

/**
 * Интерпретирует и выполняет Task (монадическую цепочку)
 * @param {Object} task - Scott-encoded Task
 * @param {Function} onSuccess - callback при успехе (value)
 * @param {Function} onError - callback при ошибке (string)
 */
function executeTask(task, onSuccess, onError) {
  task({
    // pure(a) - успешное завершение
    'pure': (value) => {
      onSuccess(value);
    },

    // fail(e) - ошибка
    'fail': (error) => {
      onError(error);
    },

    // httpGet(url, onOk, onErr) - HTTP GET с continuation
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => {
          // Продолжаем с результатом
          const nextTask = onOk(text);
          executeTask(nextTask, onSuccess, onError);
        })
        .catch((error) => {
          // Продолжаем с ошибкой (onErr continuation)
          const nextTask = onErr(error.message);
          executeTask(nextTask, onSuccess, onError);
        });
    },

    // httpPost(url, body, onOk, onErr) - HTTP POST с continuation
    'httpPost': (url, body, onOk, onErr) => {
      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body
      })
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => {
          const nextTask = onOk(text);
          executeTask(nextTask, onSuccess, onError);
        })
        .catch((error) => {
          const nextTask = onErr(error.message);
          executeTask(nextTask, onSuccess, onError);
        });
    }
  });
}

/**
 * Интерпретирует и выполняет команду (Cmd)
 * @param {Object} cmd - Scott-encoded Cmd
 * @param {Function} dispatch - функция отправки сообщений
 */
function executeCmd(cmd, dispatch) {
  cmd({
    // ε - пустая команда
    'ε': () => {},

    // _<>_ - композиция команд (параллельное выполнение)
    '_<>_': (cmd1, cmd2) => {
      executeCmd(cmd1, dispatch);
      executeCmd(cmd2, dispatch);
    },

    // httpGet - HTTP GET запрос (простой API)
    'httpGet': (url, onSuccess, onError) => {
      fetch(url)
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },

    // httpPost - HTTP POST запрос (простой API)
    'httpPost': (url, body, onSuccess, onError) => {
      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body
      })
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },

    // attempt - запуск Task (монадический API)
    // Result: ok(value) или err(error)
    'attempt': (task, handler) => {
      executeTask(
        task,
        // onSuccess: Result.ok
        (value) => {
          const result = (cb) => cb['ok'](value);
          dispatch(handler(result));
        },
        // onError: Result.err
        (error) => {
          const result = (cb) => cb['err'](error);
          dispatch(handler(result));
        }
      );
    }
  });
}

/**
 * Запуск приложения
 * @param {Object} app - Скомпилированное Agda приложение
 * @param {HTMLElement} container - DOM контейнер
 * @returns {Object} - API для управления приложением
 */
export function runApp(app, container) {
  // Состояние приложения
  let model = app.init;
  let currentVdom = null;
  let currentDom = null;
  let currentSubscription = null;
  let isUpdating = false;
  let pendingMessages = [];

  // Диспетчер сообщений
  function dispatch(msg) {
    if (isUpdating) {
      // Накапливаем сообщения во время обновления
      pendingMessages.push(msg);
      return;
    }

    isUpdating = true;

    try {
      // Получаем команду ДО обновления модели (чтобы command имел доступ к старой модели)
      const cmd = app.command(msg)(model);

      // Обновляем модель
      model = app.update(msg)(model);

      // Выполняем команду
      executeCmd(cmd, dispatch);

      // Перерисовываем
      render();

      // Обновляем подписки
      updateSubscriptions();

      // Обрабатываем накопленные сообщения
      while (pendingMessages.length > 0) {
        const nextMsg = pendingMessages.shift();
        const nextCmd = app.command(nextMsg)(model);
        model = app.update(nextMsg)(model);
        executeCmd(nextCmd, dispatch);
        render();
        updateSubscriptions();
      }
    } finally {
      isUpdating = false;
    }
  }

  // Рендеринг
  function render() {
    const newVdom = app.view(model);

    if (currentDom === null) {
      // Первый рендер
      currentDom = createElement(newVdom, dispatch);
      container.appendChild(currentDom);
    } else {
      // Патчинг
      currentDom = patch(currentDom, currentVdom, newVdom, dispatch);
    }

    currentVdom = newVdom;
  }

  // Обновление подписок на события
  // Простая стратегия: отписаться от всего, подписаться заново
  // (Event AST immutable, поэтому это безопасно)
  function updateSubscriptions() {
    // Отписываемся от старых
    if (currentSubscription) {
      unsubscribe(currentSubscription);
    }

    // Получаем новый Event AST (subs = subscriptions)
    const eventSpec = app.subs(model);

    // Интерпретируем и подписываемся
    currentSubscription = interpretEvent(eventSpec, dispatch);
  }

  // Инициализация
  render();
  updateSubscriptions();

  // Публичный API
  return {
    // Отправить сообщение
    dispatch,

    // Получить текущую модель
    getModel: () => model,

    // Получить текущий DOM
    getContainer: () => container,

    // Принудительный ререндер
    forceRender: render,

    // Уничтожение приложения
    destroy: () => {
      if (currentSubscription) {
        unsubscribe(currentSubscription);
        currentSubscription = null;
      }
      container.innerHTML = '';
    }
  };
}

// Re-export для удобства
export { createElement, patch } from './dom.js';
export { interpretEvent, subscribe, unsubscribe, debounce, throttle } from './events.js';
